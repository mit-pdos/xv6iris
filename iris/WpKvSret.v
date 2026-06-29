From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore WpGprMret WpGprSret WpKvJal.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvSret.v — wp_kv_sret, the kernelvec `sret` @0x8000542c (4-byte NON-RVC,
   Supervisor superpage).  Fetches F_Base, executes SRET (exec_execute_SRET),
   returning to PC = aligned sepc in privilege `newpriv` (= if SPP then
   Supervisor else User).  Forward engine is the BASE (non-RVC) Supervisor
   step with an ABSTRACT post-execute state sX. *)

Section ForwardSRETsup.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (sX : mstate).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
    exec (ext_decode w) s0 = Some (SRET tt, s0).
  Hypothesis Hdisp_s : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b) = Some (None, set_reg s (R_bool minstret_increment) b).
  Hypothesis HexecS :
    exec (execute (SRET tt)) (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
      = Some (RETIRE_SUCCESS, sX).
  Hypothesis Hhart_X : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_X : register_lookup (R_bool minstret_increment) sX.(sregs) = b.

  Definition sAsr : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcsr : mstate := set_reg sAsr nextPC (add_vec_int pc 4).
  Definition sTsr : mstate := set_reg sX PC (register_lookup nextPC sX.(sregs)).
  Definition sFsr : mstate :=
    if b then set_reg sTsr minstret (add_vec_int (register_lookup minstret sTsr.(sregs)) 1)
         else sTsr.

  Lemma forward_exec_sret_sup :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFsr).
  Proof using All.
    intros Lpc Lpriv Lhs Lelp.
    assert (LpcA  : register_lookup PC sAsr.(sregs) = pc).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAsr.(sregs) = Supervisor).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAsr.(sregs) = HART_ACTIVE tt).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAsr.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HfetchA : exec (fetch tt) sAsr = Some (F_Base w, sAsr)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAsr = Some (SRET tt, sAsr)) by (apply Hdec; exact LprivA).
    assert (HexecA : exec (execute (SRET tt)) s_pcsr = Some (RETIRE_SUCCESS, sX)) by exact HexecS.
    assert (Hha : exec (run_hart_active 0) sAsr = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX)).
    { exact (exec_hart_active_progress_gen root_ppn Supervisor sAsr sAsr sX sAsr w
               (SRET tt) pc RETIRE_SUCCESS
               LprivA Hdisp_s HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    apply (exec_riscv_step_gen_gen Supervisor s sX (zero_extend' 32 w) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - exact Hhart_X.
    - exact Hmi_X.
    - reflexivity.
  Qed.
End ForwardSRETsup.

Section KVSRET.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

  (* the SRET post-execute CSR tower, as a function of the initial CSRs *)
  Definition sret_ms1 (ms0 : mword 64) := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
  Definition sret_ms2 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms1 ms0) 5 5 ('b"1").
  Definition sret_newpriv (ms0 : mword 64) : Privilege :=
    if eq_vec (_get_Mstatus_SPP (sret_ms2 ms0)) ('b"1") then Supervisor else User.
  Definition sret_ms3 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms2 ms0) 8 8 ('b"0").
  Definition sret_ms4 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms3 ms0) 17 17 ('b"0").
  Definition sret_ms5 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms4 ms0) 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Definition sret_elpv (ms0 : mword 64) (lpe : bool) : mword 1 :=
    if lpe then _get_Mstatus_SPELP (sret_ms4 ms0) else landing_pad_bits_backwards NO_LP_EXPECTED.
  Definition sret_tgt (sepc0 : mword 64) := update_vec_dec sepc0 0 ('b"0").

  Lemma wp_kv_sret (va : mword 64) (w : mword 32)
      (m : gmap register_bitvector_64 (mword 64))
      (misa0 mdv0 mstatus0 satp0 mie_v sepc0 : mword 64)
      (b1 lpe : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    (forall sz : mstate, exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (lpe, sz)) ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
       exec (ext_decode w) s0 = Some (SRET tt, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ sret_tgt sepc0 -∗
        gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ sret_tgt sepc0 -∗
        cur_privilege ↦ᵣ sret_newpriv mstatus0 -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ sret_ms5 mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
        elp ↦ᵣ sret_elpv mstatus0 lpe -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN HSXL Hmode Hasid Hvec5
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4 Hmatchf Hexecf
      HA0 Hord0 Hrange0f HX0 Halignf HmisaC HmisaS HisRVC HTSR0 Hlpe Hdec
      Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")     as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Hsepc")    as %Lsepc.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")    as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")     as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")    as %Lhtif.
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_Base root_ppn va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec5 Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
                 HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa' Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b1) = Some (None, set_reg s (R_bool minstret_increment) b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (set_reg s (R_bool minstret_increment) b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (set_reg s (R_bool minstret_increment) b1)).
        replace (register_lookup misa (set_reg s (R_bool minstret_increment) b1).(sregs)) with misa0.
        2:{ unfold set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int va 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpriv. }
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lms. }
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmisa. }
    assert (Lsepc_pc : register_lookup sepc s_pc.(sregs) = sepc0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lsepc. }
    pose (sX := set_reg (set_reg (set_reg (set_reg (set_reg
                  (set_reg (set_reg (set_reg s_pc mstatus (sret_ms1 mstatus0)) mstatus (sret_ms2 mstatus0))
                           cur_privilege (sret_newpriv mstatus0)) mstatus (sret_ms3 mstatus0)) mstatus (sret_ms4 mstatus0))
                  mstatus (sret_ms5 mstatus0)) elp (sret_elpv mstatus0 lpe)) nextPC (sret_tgt sepc0)).
    assert (Hsret : exec (execute (SRET tt)) s_pc = Some (RETIRE_SUCCESS, sX)).
    { rewrite (exec_execute_SRET s_pc lpe Lpriv_pc
                 ltac:(rewrite Lmisa_pc; exact HmisaS)
                 ltac:(rewrite Lms_pc; exact HTSR0)
                 ltac:(rewrite Lmisa_pc; exact HmisaC)
                 ltac:(rewrite Lms_pc; exact Hlpe)).
      unfold sX. rewrite !Lms_pc Lsepc_pc.
      unfold sret_ms1, sret_ms2, sret_newpriv, sret_ms3, sret_ms4, sret_ms5, sret_elpv, sret_tgt.
      reflexivity. }
    assert (Hhart_X : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt).
    { unfold sX, s_pc, set_reg; cbn [sregs].
      do 10 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhs. }
    assert (Hmi_X : register_lookup (R_bool minstret_increment) sX.(sregs) = b1).
    { unfold sX, s_pc, set_reg; cbn [sregs].
      do 9 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite register_lookup_set. reflexivity. }
    iModIntro.
    iExists (sFsr b1 sX). iSplitR.
    { iPureIntro.
      apply (@forward_exec_sret_sup _ _ root_ppn s va b1 w sX Hfetch_at Hsi_s Hdec Hdisp Hsret Hhart_X Hmi_X
               Lpc Lpriv Lhs).
      rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 mstatus) _ (sret_ms1 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ (R_bitvector_64 mstatus) _ (sret_ms2 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ (sret_newpriv mstatus0) with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ (R_bitvector_64 mstatus) _ (sret_ms3 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ (R_bitvector_64 mstatus) _ (sret_ms4 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ (R_bitvector_64 mstatus) _ (sret_ms5 mstatus0) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ elp _ (sret_elpv mstatus0 lpe) with "Hreg Help'") as "[Hreg Help']".
    iMod (reg_update _ nextPC _ (sret_tgt sepc0) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (sret_tgt sepc0) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFsr, sTsr.
    assert (Enpc : register_lookup nextPC sX.(sregs) = sret_tgt sepc0)
      by (unfold sX, set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    rewrite Enpc.
    assert (Emst : register_lookup minstret (set_reg sX PC (sret_tgt sepc0)).(sregs) = register_lookup minstret s.(sregs)).
    { unfold sX, s_pc, set_reg; cbn [sregs]. repeat (rewrite irrelevant_register_set; [|reg_ne]). reflexivity. }
    destruct b1.
    - rewrite Emst.
      iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold sX, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iModIntro.
      unfold sX, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

End KVSRET.
