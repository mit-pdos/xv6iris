(* WpUserLrsc.v -- U-mode LR.W / SC.W FAULT arms (LR/SC prohibited).

   With LR/SC assumed prohibited on this platform (the data region has
   PMA_reservability = RsrvNone), a LoadReserved / StoreConditional in
   user mode translates (data TLB hit) but then fails the PMA check with
   an access fault BEFORE the model's uninterpreted reservation axiom is
   reached.  The resulting Trap ExecutionResult dispatches through
   try_step_dispatch's Trap arm (exception_handler >>= set_next_pc) and
   lands in [user_trap_frame] -- exactly like ustep_illegal, but the trap
   is delivered by the Trap arm rather than handle_exception, with cause
   E_Load_Access_Fault (SAMO for SC) and xtval = the faulting data vaddr.

   The arm's spatial footprint is the plain user_frame: the fault never
   reads or writes the data bytes, so no data window is owned.  The data
   page's RAM-ness (needed for the pmp grant) and the reservability =
   RsrvNone assumption are taken as hypotheses. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeTrap UmodeFetch UmodeFetchC UmodeStep UmodeEcall UmodeFetchFault.
Require Import UptInv UmodeData MemData4 UmodeLrsc.
Require Import WpUserEcall.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserLrsc.
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
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).

  Notation lr_cause := (rv64d_types.Exception (E_Load_Access_Fault tt)).

  (* ------------------------------------------------------------------ *)
  (* USTEP case: LR.W fault (prohibited).  The word fetches (TLB hit) and *)
  (* decodes to LOADRES; its data address translates (data TLB hit) but   *)
  (* the region has reservability RsrvNone, so the PMA check faults with   *)
  (* E_Load_Access_Fault, which memory_exception turns into a Trap.  The   *)
  (* Trap arm of try_step_dispatch delivers it -- cause E_Load_Access_Fault*)
  (* stval := the faulting data vaddr eaF -- landing in [user_trap_frame]. *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_lr_fault
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (vpnD : mword 27) (ieD : uwalk_info)
      (rs1 rd : mword 5) (aq rl : bool)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
    let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    ↑minstretN ⊆ E ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false ->
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd), s0)) ->
    (* data-side facts *)
    spec !! vpnD = Some ieD ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) ->
    uw_check_ok (LoadReserved Data) ieD ->
    update_PTE_Bits (uw_pte0 ieD) (LoadReserved Data) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) ->
    is_aligned_vaddr (Virtaddr eaF) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD ->
    is_aligned_paddr (Physaddr paD) 4 = true ->
    addr_is_ram paD ->
    addr_is_ram (pa_add paD 3) ->
    (forall region s0, matching_pma_region (register_lookup pma_regions s0.(sregs)) (Physaddr paD) 4 = Some region ->
       (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone) ->
    bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_Load_Access_Fault tt)))) = true ->
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
    intros eaF paD HN Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec
           HsomeD HvecD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD
           HramD HramD3 Hresv Hdel_loadaf.
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
    assert (Hnlpad : is_lpad_instruction (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd)) = false)
      by reflexivity.
    (* the leaf facts on the stored fetch TLB entry *)
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
    (* the leaf facts on the stored DATA TLB entry (LoadReserved access) *)
    assert (HchkD' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (LoadReserved Data) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpnD ieD)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpnD ieD))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact HchkD. }
    assert (HupdD' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpnD ieD)) (LoadReserved Data)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdD. }
    assert (HpbmtD' : forall s0, exec (tlb_get_pbmt (upt_entry vpnD ieD)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpnD ieD s0 HpbmtD). }
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
    (* read rs1's value out of the frame's gpr_file (kept whole) *)
    iDestruct "Hgpr" as "[%Hdom Hfmap]".
    assert (Hm1 : g !! Regidx rs1 = Some (g !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (g !!! Regidx rs1) σ with "Hreg Hr1c") as %Hrv1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (gpr_file g) with "[Hfmap]" as "Hgpr".
    { rewrite /gpr_file. iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"]. }
    (* ---- the hit fetch at σ ---- *)
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
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
    assert (HES : exec (currentlyEnabled Ext_S) σ = Some (true, σ)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (None, σ)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none σ mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w σ σ region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 σ Hnc ltac:(lia))
                  (within_sig_false pa 4 σ Hns ltac:(lia))
                  (within_htif_false pa 4 σ Lhtif)
                  (addr_is_ram_not_dev _ Hram)
                  Hbf Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* ---- s_x = post-fetch state (nextPC ticked) ---- *)
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (LprivX : register_lookup cur_privilege s_x.(sregs) = User)
      by (unfold s_x; lk; exact Lpriv).
    assert (LmsX : register_lookup mstatus s_x.(sregs) = ms_v)
      by (unfold s_x; lk; exact Lms).
    assert (LscX : register_lookup scause s_x.(sregs) = sc_v)
      by (unfold s_x; lk; exact Lsc).
    assert (LstvecX : register_lookup stvec s_x.(sregs) = stvec_v)
      by (unfold s_x; lk; exact Lstvec).
    assert (LelpX : register_lookup elp s_x.(sregs) = elp0)
      by (unfold s_x; lk; exact Lelp).
    assert (LpcXx : register_lookup PC s_x.(sregs) = va)
      by (unfold s_x; lk; exact Lpc).
    assert (LmisaSX : eq_vec (_get_Misa_S (register_lookup misa s_x.(sregs))) ('b"1") = true).
    { unfold s_x; lk. rewrite Lmisa. exact HmisaS. }
    assert (LsatpX : register_lookup satp s_x.(sregs) = satp0)
      by (unfold s_x; lk; exact Lsatp).
    assert (LtlbX : register_lookup tlb s_x.(sregs) = tlbvec)
      by (unfold s_x; lk; exact Ltlb).
    assert (LpmpcX : register_lookup pmpcfg_n s_x.(sregs) = pmpcfg0)
      by (unfold s_x; lk; exact Lpmpc).
    assert (LpmpaX : register_lookup pmpaddr_n s_x.(sregs) = pmpaddr00)
      by (unfold s_x; lk; exact Lpmpa).
    assert (LpmaX : register_lookup pma_regions s_x.(sregs) = pmar0)
      by (unfold s_x; lk; exact Lpma).
    assert (LsenvX : register_lookup senvcfg s_x.(sregs) = mword_of_int 0)
      by (unfold s_x; lk; exact Lsenv).
    assert (LmenvX : register_lookup menvcfg s_x.(sregs) = MENVCFG_S)
      by (unfold s_x; lk; exact Lmenv').
    assert (LmisaX : register_lookup misa s_x.(sregs) = MISA_C)
      by (unfold s_x; lk; exact Lmisa').
    assert (HESX : exec (currentlyEnabled Ext_S) s_x = Some (true, s_x)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite LmisaX.
      rewrite Hmisa_val0 in HmisaS. exact HmisaS. }
    (* ---- the DATA-address fault facts at s_x ---- *)
    assert (HMPRVX : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s_x.(sregs))) ('b"1") = false)
      by (rewrite LmsX; exact HMPRV).
    assert (HMXRX : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s_x.(sregs))) ('b"0") = true)
      by (rewrite LmsX; exact HMXR).
    assert (HSXLX : _get_Mstatus_SXL (register_lookup mstatus s_x.(sregs)) = 'b"10")
      by (rewrite LmsX; exact HSXL).
    assert (HmodeX : _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s_x.(sregs))) = ('b"1000" : mword 4))
      by (rewrite LsatpX; exact Hsatpmode).
    (* eaF bridging: the model's ea (from rs1 at s_x) equals eaF *)
    assert (Hea_x : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                             else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_x.(sregs))
                            (zeros' 64) = eaF).
    { unfold s_x, set_reg, eaF; cbn [sregs].
      tmig. rewrite Hrv1. reflexivity. }
    assert (Heaeq : add_vec_int (bits_of_virtaddr (Virtaddr eaF)) (0 * 4) = eaF).
    { cbn [bits_of_virtaddr]. apply avi0_mul4. }
    (* the data translate hit (LoadReserved) at s_x, in the execute-lemma's form *)
    assert (Htr_x : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr eaF)) (0 * 4))) (LoadReserved Data)) s_x
                    = Some (Ok (Physaddr paD, PBMT_PMA, init_ext_ptw), s_x)).
    { rewrite Heaeq.
      exact (exec_translateAddr_loadres_hit_u (upt_entry vpnD ieD) vpnD eaF satp0 tlbvec s_x
               HchkD' HupdD' HpbmtD' (upt_entry_match vpnD ieD)
               LprivX HSXLX HMPRVX LsatpX Hsatpmode Hasid LtlbX HvecD HcanonD Hvpn_defD). }
    (* the EA transform (identity) at s_x *)
    assert (Htea_x : exec (transform_effective_address
              (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_x.(sregs))
                                 (zeros' 64))) (LoadReserved Data)) s_x
                    = Some (Virtaddr eaF, s_x)).
    { rewrite Hea_x.
      exact (exec_transform_effective_address_loadres_u eaF s_x
               LprivX HMPRVX HMXRX HSXLX HESX LsenvX LmenvX HmodeX). }
    (* the data pmp grant (LoadReserved) at s_x *)
    assert (HrangeDX : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s_x.(sregs)) 0)) 4)
              (uint paD) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite LpmpaX.
      exact (ram_fetch_pmp paD (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               HramD HramD3 Hpmp_cov). }
    assert (Hpmp_x : exec (pmpCheck (Physaddr paD) 4 (LoadReserved Data) User) s_x = Some (None, s_x)).
    { exact (exec_pmpCheck_user_grant_loadres paD 4 s_x
               ltac:(rewrite LpmpcX; exact HpmpA)
               ltac:(rewrite LpmpaX; exact Hpmp_ord)
               HrangeDX
               ltac:(rewrite LpmpcX; exact HpmpR)). }
    destruct (Hpma_all paD 4) as (regionD & HpmamD & _ & _ & _ & _).
    assert (HpmamDX : matching_pma_region (register_lookup pma_regions s_x.(sregs)) (Physaddr paD) 4 = Some regionD)
      by (rewrite LpmaX; exact HpmamD).
    assert (HresvX : (override_PMA (PMA_Region_attributes regionD) PBMT_PMA).(PMA_reservability) = RsrvNone)
      by (exact (Hresv regionD s_x HpmamDX)).
    (* ---- the faulting execute: LOADRES -> Trap ---- *)
    set (resf := rv64d_types.Trap (User, make_sync_exception (E_Load_Access_Fault tt) eaF, va)).
    assert (Hexec_lr : exec (execute (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd))) s_x
                       = Some (resf, s_x)).
    { pose proof (exec_execute_LOADRES_fault User rs1 rd eaF regionD s_x paD aq rl
                    Htea_x HalignD LprivX HMPRVX Htr_x Hpmp_x HpmamDX HpaalD HresvX) as HE0.
      unfold resf. rewrite LprivX LpcXx in HE0. exact HE0. }
    assert (Hha : exec (run_hart_active 0) σ = Some (Step_Execute (resf, zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x w
               (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd)) va resf
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact Hexec_lr.
      - exact I. }
    (* ---- the dispatch arm: the Trap arm of try_step_dispatch ---- *)
    assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Load_Access_Fault tt)))) = true).
    { unfold s_x; lk. rewrite Lmedl. exact Hdel_loadaf. }
    pose proof (exec_exception_handler_ne_M s_x lr_cause User va
                  (xtval_exception_value (E_Load_Access_Fault tt) eaF)
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd
                  (make_sync_exception (E_Load_Access_Fault tt) eaF)
                  eq_refl eq_refl eq_refl LmedlX) as Hehe.
    match type of Hehe with _ = Some (_, ?T) => set (s9x := T) in Hehe end.
    set (s_trap := set_reg s9x nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch (Step_Execute (resf, zero_extend' 32 w))) s_x
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch, resf. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hehe).
      unfold s_trap. apply exec_set_next_pc. }
    (* ---- ghost updates: nextPC tick, then the trap-CSR tower ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) s_x.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite LelpX. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt lr_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause lr_cause sc_v)
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
            (tval (xtval_exception_value (E_Load_Access_Fault tt) eaF))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (resf, zero_extend' 32 w)), s_x, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s9x, s_x. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s_trap, s9x, s_x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause lr_cause sc_v),
            (tval (xtval_exception_value (E_Load_Access_Fault tt) eaF)),
            va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

End WpUserLrsc.
