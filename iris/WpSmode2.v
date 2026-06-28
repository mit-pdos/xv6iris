(* WpSmode2.v -- continued Supervisor-mode instruction WPs toward main's call to
   consoleinit.  Provides REUSABLE generic S-mode RVC infrastructure:
     - forward_exec_rvc_gpr_write_gen : privilege-generic RVC gpr-write step engine
       (generalises WpSmode.forward_exec_caddi_gpr_gen to any RVC that ExecuteAs-
       expands to a base instruction writing ONE gpr);
     - wp_smode_rvc_gpr : a generic Supervisor-mode WP for any such RVC gpr-write
       (c.addi4spn / c.mv / c.addiw / c.li / ...), reusing the S-mode fetch+step
       infrastructure proven in WpSmode.v.
   Instantiate wp_smode_rvc_gpr per instruction by supplying its decode + the two
   ExecuteAs/base execute lemmas. *)
(* WpSmode.v -- the first SUPERVISOR-mode instruction after start()'s MRET,
   PROVEN (no admits): wp_smode_caddi (c.addi sp at 0x80000e82 = <main>) and the
   full S-mode fetch/step infrastructure (translationMode/translateAddr/pmpCheck/
   getPendingSet/should_inc for Supervisor), then chained to wp_kernel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpGprAddi WpAdd WpGprMret WpGprMretWp WpStartText KernelBoot WpStartChain WpStart2 WpStart3.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

Require Import WpSmode.

Section S2.
  Context `{!riscvGS Σ}.

Section ForwardRvcGprWrite_gen.
  Context (priv : Privilege) (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (wrd : mword 5) (wval : mword 64).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w16, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret priv) s = Some (b, s).
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (cinstr, s0).
  Hypothesis Hcexec1 : exec (execute cinstr) (s_pcl s pc b)
                       = Some (ExecuteAs base, s_pcl s pc b).
  Hypothesis Hcexec2 : exec (execute base) (s_pcl s pc b)
    = Some (RETIRE_SUCCESS,
            set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval)).

  Definition sXg : mstate :=
    set_reg (s_pcl s pc b) (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval).
  Definition sTg : mstate := set_reg sXg PC (register_lookup nextPC sXg.(sregs)).
  Definition sFg : mstate :=
    if b then set_reg sTg minstret (add_vec_int (register_lookup minstret sTg.(sregs)) 1)
         else sTg.

  Lemma forward_exec_rvc_gpr_write_gen :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = priv ->
    exec (dispatchInterrupt priv) (sAl s b) = Some (None, (sAl s b)) ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFg).
  Proof using All.
    intros Lpc Lpriv Hdisp Lhs LS Lelp Lmisa.
    assert (LpcA  : register_lookup PC (sAl s b).(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege (sAl s b).(sregs) = priv).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state (sAl s b).(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact LS | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp (sAl s b).(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa (sAl s b).(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt priv) (sAl s b) = Some (None, (sAl s b))) by exact Hdisp.
    assert (HfetchA : exec (fetch tt) (sAl s b) = Some (F_RVC w16, (sAl s b))) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode_compressed w16) (sAl s b) = Some (cinstr, (sAl s b)))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) (sAl s b) = Some (true, (sAl s b)))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) (sAl s b)
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXg)).
    { exact (exec_hart_active_progress_RVC_gen priv (sAl s b) sXg w16 cinstr base pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    apply (exec_riscv_step_gen_gen priv s sXg (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXg, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXg, s_pcl, sAl; cbn zeta. trans_mi. trans_mi. rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardRvcGprWrite_gen.


  Lemma wp_smode_rvc_gpr (pc : mword 64) (w16 : mword 16)
      (cinstr base : instruction) (wrd : mword 5) (wval : mword 64)
      (m : gmap register_bitvector_64 (mword 64)) (vold misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint wrd <> 0 ->
    m !! gpr_of_Z (uint wrd) = Some vold ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (fetch_pa pc)) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (cinstr, s0)) ->
    (forall s0, exec (execute cinstr) s0 = Some (ExecuteAs base, s0)) ->
    (forall s0, exec (execute base) s0
       = Some (RETIRE_SUCCESS, set_reg s0 (R_bitvector_64 (gpr_of_Z (uint wrd))) (regval_into_reg wval))) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint wrd) := regval_into_reg wval]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd HsatpM HSXL Hpmaall HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf
             HisRVC HmisaC HmisaS Hdec Hcexec1 Hcexec2 Hb1 Hmie_mdl HSIE Help)
      "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2_S pc satp0 mstatus0 w16 region_f pmpcfg0 pmpaddr00 pmar0 b1 misa0 s (DfracOwn 1)
                 Hmatchf Hexecf HSXL HsatpM HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hms Hsatp Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (sAl s b1) = Some (None, sAl s b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (sAl s b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (sAl s b1)).
        replace (register_lookup misa (sAl s b1).(sregs)) with misa0.
        2:{ unfold sAl, set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    iModIntro.
    iExists (WpRvc.sFcg s pc b1 wrd wval (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (WpRvc.sFg_eq s pc b1 wrd wval (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write_gen Supervisor s pc b1 w16 cinstr base wrd wval
               Hfetch_at Hsi_s Hdec (Hcexec1 _) (Hcexec2 _) Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint wrd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "Hrdc") as "Hfile".
    unfold WpRvc.sFcg, WpRvc.base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

  Lemma gpr_addi_val_self_file (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (imm : mword 12) (va : mword 64) :
    uint rd <> 0 ->
    register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) s.(sregs) = va ->
    gpr_addi_val rd imm (s_pcl s pc b) = add_vec va (sign_extend' 64 imm).
  Proof.
    intros H1 Lva.
    rewrite (gpr_addi_val_lookup rd imm (s_pcl s pc b) H1).
    unfold s_pcl, sAl. unfold set_reg; cbn [sregs].
    do 2 gpr_trans. rewrite Lva. reflexivity.
  Qed.


  (* Generic Supervisor-mode WP for an RVC ADDI-family self-write (rs1 = rd):
     c.addi / c.addi16sp / ... — any compressed instr that ExecuteAs-expands to
     ITYPE (imm12, rd, rd, ADDI).  Generalises wp_smode_caddi to an arbitrary
     12-bit immediate, reusing the generic forward engine. *)
  Lemma wp_smode_addi (pc : mword 64) (w16 : mword 16)
      (cinstr : instruction) (rd : mword 5) (imm12 : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"0000" : mword 4) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (fetch_pa pc)) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC w16 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (cinstr, s0)) ->
    (forall s0, exec (execute cinstr) s0
       = Some (ExecuteAs (ITYPE (imm12, Regidx rd, Regidx rd, ADDI)), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec vd (sign_extend' 64 imm12))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int pc 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd HsatpM HSXL Hpmaall HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf
             HisRVC HmisaC HmisaS Hdec Hcexec1 Hb1 Hmie_mdl HSIE Help)
      "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC2_S pc satp0 mstatus0 w16 region_f pmpcfg0 pmpaddr00 pmar0 b1 misa0 s (DfracOwn 1)
                 Hmatchf Hexecf HSXL HsatpM HA0 Hord0 Hrange0 HX0 Halignf Hbit0f Hbit1f Hvalignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hmisa' Hms Hsatp Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (sAl s b1) = Some (None, sAl s b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (sAl s b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (sAl s b1)).
        replace (register_lookup misa (sAl s b1).(sregs)) with misa0.
        2:{ unfold sAl, set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    assert (Hcexec2' : exec (execute (ITYPE (imm12, Regidx rd, Regidx rd, ADDI))) (s_pcl s pc b1)
                       = Some (RETIRE_SUCCESS, set_reg (s_pcl s pc b1)
                                 (R_bitvector_64 (gpr_of_Z (uint rd)))
                                 (regval_into_reg (add_vec vd (sign_extend' 64 imm12))))).
    { rewrite (exec_execute_ITYPE_ADDI_gpr rd rd imm12 (s_pcl s pc b1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite (gpr_addi_val_self_file s pc b1 rd imm12 vd Hrd Lrd). reflexivity. }
    iModIntro.
    iExists (WpRvc.sFcg s pc b1 rd (add_vec vd (sign_extend' 64 imm12)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (WpRvc.sFg_eq s pc b1 rd (add_vec vd (sign_extend' 64 imm12)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write_gen Supervisor s pc b1 w16 cinstr
               (ITYPE (imm12, Regidx rd, Regidx rd, ADDI)) rd (add_vec vd (sign_extend' 64 imm12))
               Hfetch_at Hsi_s Hdec (Hcexec1 (s_pcl s pc b1)) Hcexec2' Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec vd (sign_extend' 64 imm12))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vd (sign_extend' 64 imm12))) with "Hrdc") as "Hfile".
    unfold WpRvc.sFcg, WpRvc.base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

End S2.
