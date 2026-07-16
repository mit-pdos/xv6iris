(* WpUserSplitFault.v -- the 2-aligned HIGH-HALF fetch fault USTEP arm.

   At a pc == 2 (mod 4) address holding a 32-bit F_Base instruction, the
   fetch is a split (2+2) fetch: the LOW halfword at [va] translates +
   reads OK (state-preserving TLB hit), but the HIGH halfword at [va+2]
   FAILS its INDEPENDENT translate (unmapped / no-permission leaf).  The
   model credits the fault to the HIGH granule -- [fetch] reports
   [F_Error (E_Fetch_Page_Fault, va+2)] -- so the trap is delivered with
   sepc = va (the PC) but stval = va+2 (the faulting fetch address).

   [ustep_split_highfault] rides the model lemma
   [exec_fetch_F_Base_2_U_highfault_gen] (UmodeFetchC.v).  Its LOW-half
   fetch-hit premise bundle is [wp_instr_u_split]'s low bundle; its
   HIGH-half fault premise is the [ustep_noexec_fetch_fault] denial
   ([spec !! vpnH = Some ieH], [uw_check_denied]).  The trap-delivery
   tower is [ustep_noexec_fetch_fault]'s, with the reported fault address
   va -> va+2 (sepc stays va).                                           *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeTrap UmodeFetch UmodeFetchC UmodeStep UmodeFetchFault UmodeWalk.
Require Import UptInv WpUserLoop.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.
Require Import WpUserFetch.

Section WpUserSplitFault.
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
  Local Notation upt_translateAddr_fetch_noexec :=
    (WpUserFetch.upt_translateAddr_fetch_noexec U).

  Notation pf_cause := (rv64d_types.Exception (E_Fetch_Page_Fault tt)).

  (* ------------------------------------------------------------------ *)
  (* USTEP case: 2-aligned (pc == 2 mod 4) 32-bit F_Base fetch whose HIGH  *)
  (* halfword page-faults.  The LOW half hits + reads (state-preserving);  *)
  (* the HIGH half's translate is DENIED (no X / no U leaf), so the fetch  *)
  (* reports F_Error at va+2.  Delivered by the fetch-fault trap tower     *)
  (* (Step_Fetch_Failure -> handle_exception), sepc = va, stval = va+2.    *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_split_highfault
      (va : mword 64) (vpnL vpnH : mword 27) (ieL ieH : uwalk_info)
      (ilo : mword 16)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
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
         = Some (nth_byte ilo j)) ->
    isRVC ilo = false ->
    (* HIGH half fetch FAULT: va+2 -> vpnH mapped-but-denied *)
    spec !! vpnH = Some ieH ->
    uw_check_denied (InstructionFetch tt) ieH ->
    upt_tlb_ok spec tlbvec ->
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
    (* high half canon / vpn *)
    neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnH ->
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
    intros HN HvecL Hchk0L HupdNL Hpbmt0L HcwL HnotRVC
           HsomeH HdenH Hok HSXL
           Hbit0 Hbit1 Hvalign4
           HcanonL Hvpn_defL HalignL
           HcanonH Hvpn_defH.
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
    (* the LOW-half leaf facts, transported onto the stored TLB entry *)
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
    iApply (wp_exec_step_trapish_inv E Φ HN with "Hinv Hhs").
    iIntros (σ) "[Hreg Hmem]".
    iDestruct "Hmem" as "[Hmem Hdev]".
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
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    (* ---- the LOW-half code page: bytes + RAM-ness ---- *)
    set (palv := u_pa (upt_entry vpnL ieL) va vpnL) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               σ.(mem) !! (pa_add palv j) = Some (nth_byte ilo j)⌝)%I as %HbfL.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (HcwL j ltac:(lia)) with "Hcode") as "Hbj".
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
    pose proof (addr_is_ram_not_in_clint _ HramL) as HncL.
    pose proof (addr_is_ram_not_in_sig _ HramL) as HnsL.
    (* ---- pure facts at σ ---- *)
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
    (* shared PMP facts (pmpcfg / pmpaddr at σ, address-independent) *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hpmp_cov).
    (* the LOW-half TLB-hit translate (state-preserving) *)
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpnL ieL) vpnL HchkL' HupdL'
                  HpbmtL' (upt_entry_match vpnL ieL) va satp0 tlbvec σ
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb HvecL HcanonL Hvpn_defL) as HtrL.
    (* the LOW-half PMP range + PMA region *)
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
    (* the HIGH-half fault translate at va+2, borrowing the state interp *)
    iAssert (⌜exec (translateAddr (Virtaddr (add_vec_int va 2)) (InstructionFetch tt)) σ
               = Some (Err (E_Fetch_Page_Fault tt, tt), σ)⌝)%I as %Htr_high.
    { iApply (upt_translateAddr_fetch_noexec vpnH ieH (add_vec_int va 2) tlbvec σ
                HsomeH HdenH Hok Lpriv HSXL' Lsatp Ltlb HcanonH Hvpn_defH
                HA' Hord' HR' Hcov'
                with "Hhw [Hreg Hmem Hdev] Hupt"). iFrame. }
    (* the split (2+2) fetch: low OK, high faults -> F_Error at va+2 *)
    pose proof (exec_fetch_F_Base_2_U_highfault_gen va palv ilo (E_Fetch_Page_Fault tt)
                  σ σ regl
                  Lpc Lpc HmisaC' Hbit0 Hbit1 Hvalign4 HtrL
                  HA' Hord' HrangeL' HX' HpmamL' HalignL HpmaxL
                  (within_clint_false palv 2 σ HncL ltac:(lia))
                  (within_sig_false palv 2 σ HnsL ltac:(lia))
                  (within_htif_false palv 2 σ Lhtif)
                  (addr_is_ram_not_dev _ HramL) HbfL Lpriv
                  Htr_high HnotRVC) as Hfetch.
    pose proof (exec_run_hart_active_fetch_fault σ User (E_Fetch_Page_Fault tt) (add_vec_int va 2)
                  Lpriv Hdisp Hfetch) as Hha.
    (* the dispatch arm: handle_exception at σ (sepc = va, stval = va+2) *)
    assert (LmisaS : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS).
    assert (Lmedl' : bit_to_bool (access_vec_dec (register_lookup medeleg σ.(sregs))
                       (uint (exceptionType_bits_forwards (E_Fetch_Page_Fault tt)))) = true)
      by (rewrite Lmedl; exact Hdel_fetchpf).
    pose proof (exec_handle_exception_ne_M σ pf_cause User va
                  (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr (add_vec_int va 2))))
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) Lpriv Lms Lsc Lstvec Lelp LmisaS Htvd Lpc
                  (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (E_Fetch_Page_Fault tt)
                  eq_refl eq_refl Lmedl') as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch (Step_Fetch_Failure (Virtaddr (add_vec_int va 2), E_Fetch_Page_Fault tt))) σ
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    (* ---- ghost updates in tower order ---- *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    assert (Hlkelp : register_lookup elp
              (register_set mstatus (update_subrange_vec_dec ms_v 23 23 elp0) σ.(sregs))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite Lelp. exact Help0. }
    iDestruct (reg_interp_set_same _ elp _ Hlkelp with "Hreg") as "Hreg".
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt pf_cause)))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause pf_cause sc_v)
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
            (tval (xtval_exception_value (E_Fetch_Page_Fault tt) (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Fetch_Failure (Virtaddr (add_vec_int va 2), E_Fetch_Page_Fault tt)), σ, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s_trap, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    assert (Hstv : tval (xtval_exception_value (E_Fetch_Page_Fault tt)
                           (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))) = add_vec_int va 2)
      by reflexivity.
    iEval (rewrite Hstv) in "Hstv".
    (* ---- repack the trap frame: stval = va+2, sepc = va ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause pf_cause sc_v), (add_vec_int va 2), va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.

End WpUserSplitFault.
