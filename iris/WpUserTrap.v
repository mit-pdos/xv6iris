(* WpUserTrap.v -- the trap USTEP arms (ECALL / illegal / breakpoint, base and compressed).
   Split from the monolithic WpUserExec.v; all lemmas close over the
   single parameter bundle [uctx] (see WpUserBase).                      *)
(* WpUserExec.v -- the user-execution theorem: the loop frames and the
   Löb skeleton.

   [user_frame] is the loop invariant P of [wp_user_loop]: an ARBITRARY
   user machine -- existential GPRs, pc, trap CSRs, TLB (consistent with
   the page-table spec) -- over the loop-constant configuration (the
   [user_cfg] cells, the page-table ownership [upt_inv], the persistent
   user code bytes, and the writable user data bytes).

   [user_trap_frame] is Tr: the same machine handed to the kernel
   re-entry continuation -- Supervisor privilege, pc at stvec's direct
   base, trap CSRs written (existential here; refined per-cause by the
   USTEP cases that produce it).

   [wp_user_exec] is the Löb capstone: one USTEP obligation -- a single
   machine step from [user_frame] re-establishes [user_frame] (retire)
   or produces [user_trap_frame] (trap), with both continuations under a
   later -- runs arbitrary user code forever.  The USTEP obligation is
   discharged case by case in the companion files (fetch trichotomy x
   decode totality x execute families); the proven instances so far are
   the wp_user_ecall / wp_user_fetch_pagefault vertical slices.        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpLeafCommon WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeTrap UmodeFetch UmodeFetchC UmodeStep UmodeEcall UmodeFetchFault UmodeWalk.
Require Import UptInv WpUserLoop WpUserEcall WpGprAddi WpGprLogic WpGprLui WpAuipc WpGprAuipc WpMmodeShiftiop WpMmodeJal WpGprJalr WpMemsetS WpHolding UmodeData WpGprLoad WpGprStore.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.

Section WpUserTrap.
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


  (* ------------------------------------------------------------------ *)
  (* USTEP case: ECALL.  The pc's vpn is mapped, hits the TLB at its walk *)
  (* entry, A bit set, the code bytes at the translated pa spell ecall -- *)
  (* the whole wp_user_ecall vertical slice, replayed against the loop    *)
  (* frames and landing in [user_trap_frame].                             *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_ecall
      (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    spec !! vpn = Some i ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) ->
    uw_check_ok (InstructionFetch tt) i ->
    update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None ->
    (* the fetched bytes are the ecall word *)
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte ecall_w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true ->
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
    intros HN Hsome Hok Hvec Hchk0 HupdN Hcw HSXL Hval Hcanon Hvpn_def Hpaal.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
             #Hcode Hdata Hcfg Hcont".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* the leaf facts, transported onto the stored TLB entry *)
    destruct (Hspec vpn i Hsome) as (_ & _ & _ & Hwf).
    destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & Hpbmt0).
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn i)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn i))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn i)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn i)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn i s0 Hpbmt0). }
    (* the persistent ecall bytes, looked up in the code image *)
    iAssert ([∗ list] j ∈ seq 0 4,
               (pa_add (u_pa (upt_entry vpn i) va vpn) j) ↦ₘ□ nth_byte ecall_w j)%I
      as "#Hbytes".
    { iApply big_sepL_intro. iIntros "!>" (k y Hky).
      apply lookup_seq in Hky. destruct Hky as [-> Hk].
      assert (Heq : (0 + k)%nat = k) by lia. rewrite Heq.
      iApply (big_sepM_lookup _ _ _ _ (Hcw k Hk) with "Hcode"). }
    iApply (wp_user_ecall (upt_entry vpn i) vpn va satp0 ms_v sc_v stval_v sepc_v
              stvec_v mie_v midl_v mip_v medl_v MENVCFG_S meip seip tlbvec
              pmpcfg0 pmpaddr00 E Φ
              HN Hmm Hs0 HSXL Hsatpmode Hasid Hvec Hchk' Hupd' Hpbmt'
              (upt_entry_match vpn i) Hval Hcanon Hvpn_def Hpaal
              HpmpA Hpmp_ord HpmpX Hpmp_cov Htvd Hdel_ecall eq_refl
              with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Hstvec Hmie Hmidl
                    Hmedl Hmip Hmeip Hseip Hsatp Htlbc Hmenv Hsenv Hmst0 Hsst0
                    Hpmpc Hpmpa Hbytes Hpc").
    iNext.
    iIntros "Hpriv Hms Hsc Hstv Hsepc Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip
             Hsatp Htlbc Hmenv Hsenv Hmst0 Hsst0 Hpmpc Hpmpa Hhs Hpc".
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (u_trap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (u_trap_cause sc_v), (tval None), va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpc".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* USTEP case: ILLEGAL INSTRUCTION (generic).  The word fetches (TLB    *)
  (* hit) and decodes, but its execute yields Illegal_Instruction -- CSR  *)
  (* accesses, SRET/MRET, FP with FS=Off: everything user code may NOT    *)
  (* do.  The delegated tower runs with cause E_Illegal_Instr and stval   *)
  (* := the instruction bits; lands in [user_trap_frame].                 *)
  (* ------------------------------------------------------------------ *)
  Notation ill_cause := (rv64d_types.Exception (E_Illegal_Instr tt)).


  Lemma ustep_illegal (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op is illegal in this state, with NO state change *)
    (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_ill Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec.
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
    (* the leaf facts on the stored TLB entry *)
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
    (* ---- the whole non-retiring step: execute -> Illegal ---- *)
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x w ii va
               (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact (Hexec_ill s_x).
      - exact I. }
    (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
    assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
    { unfold s_x; lk. rewrite Lmedl. exact Hdel_illegal. }
    pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                  (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd LpcXx
                  (zero_extend' 64 (zero_extend' 32 w)) (E_Illegal_Instr tt)
                  eq_refl eq_refl LmedlX) as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch
                       (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w))) s_x
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    (* ---- ghost updates: nextPC tick, then the tower ---- *)
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
    (* ---- repack the trap frame ---- *)
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


  Lemma ustep_illegal_st (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op is illegal whenever executing in User mode (SRET/MRET/WFI/
       SFENCE*: the model reads cur_privilege and yields Illegal) *)
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_ill Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec.
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
    (* the leaf facts on the stored TLB entry *)
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
    (* ---- the whole non-retiring step: execute -> Illegal ---- *)
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (LprivXe : register_lookup cur_privilege s_x.(sregs) = User)
      by (unfold s_x; lk; exact Lpriv).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x w ii va
               (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact (Hexec_ill s_x LprivXe).
      - exact I. }
    (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
    assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
    { unfold s_x; lk. rewrite Lmedl. exact Hdel_illegal. }
    pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                  (xtval_exception_value (E_Illegal_Instr tt)
                     (zero_extend' 64 (zero_extend' 32 w)))
                  ms_v sc_v stvec_v elp0
                  (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd LpcXx
                  (zero_extend' 64 (zero_extend' 32 w)) (E_Illegal_Instr tt)
                  eq_refl eq_refl LmedlX) as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
    assert (Hdispb : exec (try_step_dispatch
                       (Step_Execute (Illegal_Instruction tt, zero_extend' 32 w))) s_x
                     = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match. exact Hhe. }
    (* ---- ghost updates: nextPC tick, then the tower ---- *)
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
    (* ---- repack the trap frame ---- *)
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


  Lemma ustep_ebreak (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (w : mword 32)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the instruction traps to a software breakpoint (EBREAK-like) *)
    (forall s, register_lookup cur_privilege s.(sregs) = User ->
       register_lookup PC s.(sregs) = va ->
       exec (execute ii) s
         = Some (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s)) ->
    is_lpad_instruction ii = false ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_bp Hnlpad Hok Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon
           Hvpn_def Hpaal HnotRVC Hdec.
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
    (* the leaf facts on the stored TLB entry *)
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
    (* ---- the whole non-retiring step: execute -> Illegal ---- *)
    set (s_x := set_reg σ nextPC (add_vec_int va 4)).
    assert (LprivXe : register_lookup cur_privilege s_x.(sregs) = User)
      by (unfold s_x; lk; exact Lpriv).
    assert (LpcXe : register_lookup PC s_x.(sregs) = va)
      by (unfold s_x; lk; exact Lpc).
    assert (Hha : exec (run_hart_active 0) σ
                    = Some (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                          zero_extend' 32 w), s_x)).
    { apply (exec_hart_active_progress_base_gen User σ σ s_x w ii va
               (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va))
               Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact (Hexec_bp s_x LprivXe LpcXe).
      - exact I. }
    (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
    assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                       (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true).
    { unfold s_x; lk. rewrite Lmedl. exact Hdel_break. }
    pose proof (exec_exception_handler_ne_M s_x (rv64d_types.Exception (E_Breakpoint Brk_Software)) User va
                    (xtval_exception_value (E_Breakpoint Brk_Software) va)
                    ms_v sc_v stvec_v elp0
                    (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd
                    (make_sync_exception (E_Breakpoint Brk_Software) va)
                    eq_refl eq_refl eq_refl LmedlX) as Hhe.
    match type of Hhe with _ = Some (_, ?T) => set (s_mid := T) in Hhe end.
    set (s_trap := set_reg s_mid nextPC (stvec_base stvec_v)).
    assert (Hdispb : exec (try_step_dispatch
                         (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                        zero_extend' 32 w))) s_x
                       = Some (tt, s_trap)).
    { unfold try_step_dispatch. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Hhe). apply exec_set_next_pc. }
    (* ---- ghost updates: nextPC tick, then the tower ---- *)
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
               (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception (E_Breakpoint Brk_Software)))))
            with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v)
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
            (tval (xtval_exception_value (E_Breakpoint Brk_Software) va))
            with "Hreg Hstv") as "[Hreg Hstv]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                            zero_extend' 32 w)), s_x, s_trap.
    iSplitR; [iPureIntro; exact Hha |].
    iSplitR; [iPureIntro; exact Hdispb |].
    iSplitR; [iPureIntro; reflexivity |].
    assert (LpcT : register_lookup PC s_trap.(sregs) = va).
    { unfold s_trap, s_mid, s_x. lk. exact Lpc. }
    rewrite LpcT.
    iSplitL "Hpcr"; [iExact "Hpcr" |].
    iSplitL "Hreg Hmem Hdev".
    { unfold s_trap, s_mid, s_x, set_reg; cbn [sregs mem mdev].
      unfold utrap_ms, utrap_scause.
      iFrame "Hreg Hmem Hdev". }
    iNext.
    iIntros "Hhs Hpcr".
    assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
    { unfold s_trap, s_mid. lk. reflexivity. }
    rewrite LnT.
    rewrite Help0.
    (* ---- repack the trap frame ---- *)
    iApply "Hcont".
    rewrite /user_trap_frame.
    iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
            (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v),
            (tval (xtval_exception_value (E_Breakpoint Brk_Software) va)),
            va, g, tlbvec.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
    iSplitR; [iPureIntro; exact Hok |].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
    iFrame "Hpcr Hnpc".
  Qed.


  Lemma ustep_c_ebreak (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the compressed instruction expands to a breakpoint trap *)
    (forall s : mstate, exec (execute ii) s = Some (ExecuteAs (EBREAK tt), s)) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
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
    intros HN Hexp Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec.
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
    (* the leaf facts on the stored TLB entry *)
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
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
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
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HZca : exec (currentlyEnabled Ext_Zca) σ = Some (true, σ)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa. exact HmisaC. }
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    destruct Hmode as
      [ (w4 & Hval & Hpaal & Hcw & Hh_eq)
      | (Hb0 & Hb1 & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, F_RVC is the low half *)
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
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ region
                 Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ Hnc ltac:(lia))
                 (within_sig_false pa 4 σ Hns ltac:(lia))
                 (within_htif_false pa 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv).
        rewrite <- Hh_eq. exact HisRVC. }
      set (s_x := set_reg σ nextPC (add_vec_int va 2)).
      assert (LprivXe : register_lookup cur_privilege s_x.(sregs) = User)
        by (unfold s_x; lk; exact Lpriv).
      assert (LpcXe : register_lookup PC s_x.(sregs) = va)
        by (unfold s_x; lk; exact Lpc).
      assert (HexecB : exec (execute (EBREAK tt)) s_x
                = Some (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s_x))
        by (apply exec_execute_EBREAK_U; [exact LprivXe | exact LpcXe]).
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                            zero_extend' 32 h), s_x)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_x h ii (EBREAK tt) va
                 (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va))
                 Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact HexecB. }
      (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
      assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                         (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true).
      { unfold s_x; lk. rewrite Lmedl. exact Hdel_break. }
      pose proof (exec_exception_handler_ne_M s_x (rv64d_types.Exception (E_Breakpoint Brk_Software)) User va
                    (xtval_exception_value (E_Breakpoint Brk_Software) va)
                    ms_v sc_v stvec_v elp0
                    (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd
                    (make_sync_exception (E_Breakpoint Brk_Software) va)
                    eq_refl eq_refl eq_refl LmedlX) as Hhe.
      match type of Hhe with _ = Some (_, ?T) => set (s_mid := T) in Hhe end.
      set (s_trap := set_reg s_mid nextPC (stvec_base stvec_v)).
      assert (Hdispb : exec (try_step_dispatch
                         (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                        zero_extend' 32 h))) s_x
                       = Some (tt, s_trap)).
      { unfold try_step_dispatch. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ Hhe). apply exec_set_next_pc. }
      (* ---- ghost updates: nextPC tick, then the tower ---- *)
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
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
                 (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception (E_Breakpoint Brk_Software)))))
              with "Hreg Hsc") as "[Hreg Hsc]".
      iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v)
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
              (tval (xtval_exception_value (E_Breakpoint Brk_Software) va))
              with "Hreg Hstv") as "[Hreg Hstv]".
      iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                              zero_extend' 32 h)), s_x, s_trap.
      iSplitR; [iPureIntro; exact Hha |].
      iSplitR; [iPureIntro; exact Hdispb |].
      iSplitR; [iPureIntro; reflexivity |].
      assert (LpcT : register_lookup PC s_trap.(sregs) = va).
      { unfold s_trap, s_mid, s_x. lk. exact Lpc. }
      rewrite LpcT.
      iSplitL "Hpcr"; [iExact "Hpcr" |].
      iSplitL "Hreg Hmem Hdev".
      { unfold s_trap, s_mid, s_x, set_reg; cbn [sregs mem mdev].
        unfold utrap_ms, utrap_scause.
        iFrame "Hreg Hmem Hdev". }
      iNext.
      iIntros "Hhs Hpcr".
      assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
      { unfold s_trap, s_mid. lk. reflexivity. }
      rewrite LnT.
      rewrite Help0.
      (* ---- repack the trap frame ---- *)
      iApply "Hcont".
      rewrite /user_trap_frame.
      iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
              (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v),
              (tval (xtval_exception_value (E_Breakpoint Brk_Software) va)),
              va, g, tlbvec.
      iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
      iSplitR; [iPureIntro; exact Hok |].
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
      iFrame "Hpcr Hnpc".
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
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ region
                 Lpc Hb0 Hb1 Hval4 HmisaC' Htr HA' Hord' Hrange' HX' Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ Hnc ltac:(lia))
                 (within_sig_false pa 2 σ Hns ltac:(lia))
                 (within_htif_false pa 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv HisRVC). }
      set (s_x := set_reg σ nextPC (add_vec_int va 2)).
      assert (LprivXe : register_lookup cur_privilege s_x.(sregs) = User)
        by (unfold s_x; lk; exact Lpriv).
      assert (LpcXe : register_lookup PC s_x.(sregs) = va)
        by (unfold s_x; lk; exact Lpc).
      assert (HexecB : exec (execute (EBREAK tt)) s_x
                = Some (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s_x))
        by (apply exec_execute_EBREAK_U; [exact LprivXe | exact LpcXe]).
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                            zero_extend' 32 h), s_x)).
      { apply (exec_hart_active_progress_RVC_gen User σ σ s_x h ii (EBREAK tt) va
                 (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va))
                 Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca).
        - apply Hexp.
        - exact HexecB. }
      (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
      assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                         (uint (exceptionType_bits_forwards (E_Breakpoint Brk_Software)))) = true).
      { unfold s_x; lk. rewrite Lmedl. exact Hdel_break. }
      pose proof (exec_exception_handler_ne_M s_x (rv64d_types.Exception (E_Breakpoint Brk_Software)) User va
                    (xtval_exception_value (E_Breakpoint Brk_Software) va)
                    ms_v sc_v stvec_v elp0
                    (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd
                    (make_sync_exception (E_Breakpoint Brk_Software) va)
                    eq_refl eq_refl eq_refl LmedlX) as Hhe.
      match type of Hhe with _ = Some (_, ?T) => set (s_mid := T) in Hhe end.
      set (s_trap := set_reg s_mid nextPC (stvec_base stvec_v)).
      assert (Hdispb : exec (try_step_dispatch
                         (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                                        zero_extend' 32 h))) s_x
                       = Some (tt, s_trap)).
      { unfold try_step_dispatch. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ Hhe). apply exec_set_next_pc. }
      (* ---- ghost updates: nextPC tick, then the tower ---- *)
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
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
                 (bool_to_bit (trapCause_is_interrupt (rv64d_types.Exception (E_Breakpoint Brk_Software)))))
              with "Hreg Hsc") as "[Hreg Hsc]".
      iMod (reg_update _ scause _ (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v)
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
              (tval (xtval_exception_value (E_Breakpoint Brk_Software) va))
              with "Hreg Hstv") as "[Hreg Hstv]".
      iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists (Step_Execute (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va),
                              zero_extend' 32 h)), s_x, s_trap.
      iSplitR; [iPureIntro; exact Hha |].
      iSplitR; [iPureIntro; exact Hdispb |].
      iSplitR; [iPureIntro; reflexivity |].
      assert (LpcT : register_lookup PC s_trap.(sregs) = va).
      { unfold s_trap, s_mid, s_x. lk. exact Lpc. }
      rewrite LpcT.
      iSplitL "Hpcr"; [iExact "Hpcr" |].
      iSplitL "Hreg Hmem Hdev".
      { unfold s_trap, s_mid, s_x, set_reg; cbn [sregs mem mdev].
        unfold utrap_ms, utrap_scause.
        iFrame "Hreg Hmem Hdev". }
      iNext.
      iIntros "Hhs Hpcr".
      assert (LnT : register_lookup nextPC s_trap.(sregs) = stvec_base stvec_v).
      { unfold s_trap, s_mid. lk. reflexivity. }
      rewrite LnT.
      rewrite Help0.
      (* ---- repack the trap frame ---- *)
      iApply "Hcont".
      rewrite /user_trap_frame.
      iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
              (utrap_scause (rv64d_types.Exception (E_Breakpoint Brk_Software)) sc_v),
              (tval (xtval_exception_value (E_Breakpoint Brk_Software) va)),
              va, g, tlbvec.
      iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
      iSplitR; [iPureIntro; exact Hok |].
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
      iFrame "Hpcr Hnpc".
  Qed.


  (* ------------------------------------------------------------------ *)
  (* The COMPRESSED illegal case: the decoded compressed instruction's    *)
  (* execute yields Illegal_Instruction directly (C_ILLEGAL, and any      *)
  (* future config-illegal compressed op) -> full trap to stvec.  The     *)
  (* RVC dispatch has no landing-pad-instruction check, and stval gets    *)
  (* the zero-extended HALFWORD.                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_c_illegal (ii : instruction)
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info) (h : mword 16)
      (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* the op is illegal in this state, with NO state change *)
    (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) ->
    upt_tlb_ok spec tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
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
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode_compressed h) s0 = Some (ii, s0)) ->
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
    intros HN Hexec_ill Hok Hvec Hchk0 HupdN Hpbmt0 HSXL Hcanon Hvpn_def
           Hmode HisRVC Hdec.
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
    (* the leaf facts on the stored TLB entry *)
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
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
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
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (HZca : exec (currentlyEnabled Ext_Zca) σ = Some (true, σ)).
    { apply exec_currentlyEnabled_Zca. rewrite Lmisa. exact HmisaC. }
    assert (Lmenv' : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec σ (agree_u σ Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp σ.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    destruct Hmode as
      [ (w4 & Hval & Hpaal & Hcw & Hh_eq)
      | (Hb0 & Hb1 & Hval4 & Hpaal2 & Hcw) ].
    - (* 4-aligned: full 4-byte window, F_RVC is the low half *)
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
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram3 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 4 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { rewrite Hh_eq.
        apply (exec_fetch_F_RVC_4_U_gen va pa w4 σ σ region
                 Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                 (within_clint_false pa 4 σ Hnc ltac:(lia))
                 (within_sig_false pa 4 σ Hns ltac:(lia))
                 (within_htif_false pa 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv).
        rewrite <- Hh_eq. exact HisRVC. }
      set (s_x := set_reg σ nextPC (add_vec_int va 2)).
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h), s_x)).
      { exact (exec_hart_active_progress_RVC_direct_gen User σ σ s_x h ii va
                 (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca
                 (Hexec_ill s_x) I). }
      (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
      assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                         (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
      { unfold s_x; lk. rewrite Lmedl. exact Hdel_illegal. }
      pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                    (xtval_exception_value (E_Illegal_Instr tt)
                       (zero_extend' 64 (zero_extend' 32 h)))
                    ms_v sc_v stvec_v elp0
                    (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd LpcXx
                    (zero_extend' 64 (zero_extend' 32 h)) (E_Illegal_Instr tt)
                    eq_refl eq_refl LmedlX) as Hhe.
      match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
      assert (Hdispb : exec (try_step_dispatch
                         (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h))) s_x
                       = Some (tt, s_trap)).
      { unfold try_step_dispatch. cbn match. exact Hhe. }
      (* ---- ghost updates: nextPC tick, then the tower ---- *)
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
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
                       (zero_extend' 64 (zero_extend' 32 h))))
              with "Hreg Hstv") as "[Hreg Hstv]".
      iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h)), s_x, s_trap.
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
      (* ---- repack the trap frame ---- *)
      iApply "Hcont".
      rewrite /user_trap_frame.
      iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
              (utrap_scause ill_cause sc_v),
              (tval (xtval_exception_value (E_Illegal_Instr tt)
                       (zero_extend' 64 (zero_extend' 32 h)))),
              va, g, tlbvec.
      iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
      iSplitR; [iPureIntro; exact Hok |].
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
      iFrame "Hpcr Hnpc".
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
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite Lpmpa.
        exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 2 1
                 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram Hram1 Hpmp_cov). }
      assert (Hpmam' : matching_pma_region (register_lookup pma_regions σ.(sregs))
                (Physaddr pa) 2 = Some region)
        by (rewrite Lpma; exact Hpmam).
      assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
        by (rewrite Lmisa; exact HmisaC).
      assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, σ)).
      { exact (exec_fetch_F_RVC_2_U_gen va pa h σ σ region
                 Lpc Hb0 Hb1 Hval4 HmisaC' Htr HA' Hord' Hrange' HX' Hpmam' Hpaal2 Hpmax
                 (within_clint_false pa 2 σ Hnc ltac:(lia))
                 (within_sig_false pa 2 σ Hns ltac:(lia))
                 (within_htif_false pa 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram)
                 Hbf Lpriv HisRVC). }
      set (s_x := set_reg σ nextPC (add_vec_int va 2)).
      assert (Hha : exec (run_hart_active 0) σ
                      = Some (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h), s_x)).
      { exact (exec_hart_active_progress_RVC_direct_gen User σ σ s_x h ii va
                 (Illegal_Instruction tt) Lpriv Hdisp Hfetch Hdec' Hlpad Lpc HZca
                 (Hexec_ill s_x) I). }
      (* ---- the dispatch arm: handle_exception at s_x ---- *)
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
      assert (LmedlX : bit_to_bool (access_vec_dec (register_lookup medeleg s_x.(sregs))
                         (uint (exceptionType_bits_forwards (E_Illegal_Instr tt)))) = true).
      { unfold s_x; lk. rewrite Lmedl. exact Hdel_illegal. }
      pose proof (exec_handle_exception_ne_M s_x ill_cause User va
                    (xtval_exception_value (E_Illegal_Instr tt)
                       (zero_extend' 64 (zero_extend' 32 h)))
                    ms_v sc_v stvec_v elp0
                    (or_introl eq_refl) LprivX LmsX LscX LstvecX LelpX LmisaSX Htvd LpcXx
                    (zero_extend' 64 (zero_extend' 32 h)) (E_Illegal_Instr tt)
                    eq_refl eq_refl LmedlX) as Hhe.
      match type of Hhe with _ = Some (_, ?T) => set (s_trap := T) in Hhe end.
      assert (Hdispb : exec (try_step_dispatch
                         (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h))) s_x
                       = Some (tt, s_trap)).
      { unfold try_step_dispatch. cbn match. exact Hhe. }
      (* ---- ghost updates: nextPC tick, then the tower ---- *)
      iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
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
                       (zero_extend' 64 (zero_extend' 32 h))))
              with "Hreg Hstv") as "[Hreg Hstv]".
      iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
      iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
      iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
      iModIntro.
      iExists (Step_Execute (Illegal_Instruction tt, zero_extend' 32 h)), s_x, s_trap.
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
      (* ---- repack the trap frame ---- *)
      iApply "Hcont".
      rewrite /user_trap_frame.
      iExists (utrap_ms ms_v (landing_pad_bits_backwards NO_LP_EXPECTED)),
              (utrap_scause ill_cause sc_v),
              (tval (xtval_exception_value (E_Illegal_Instr tt)
                       (zero_extend' 64 (zero_extend' 32 h)))),
              va, g, tlbvec.
      iFrame "Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hgpr Hupt Hcode Hdata".
      iSplitR; [iPureIntro; exact Hok |].
      rewrite /user_cfg.
      iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
              Hmst0 Hsst0 Hpmpc Hpmpa".
      iFrame "Hpcr Hnpc".
  Qed.


End WpUserTrap.
