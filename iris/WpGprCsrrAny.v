From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprCsrr.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* Generic register-generic CSR-read step: csrr rd, csr  (= csrrs rd,csr,rs1z with
   rs1z = x0).  Parameterised over the CSR; the per-CSR facts (accessibility,
   read value, callback) are supplied as hypotheses. *)
Lemma csrr_read_step (csr : mword 12) (rs1z rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  uint rs1z = 0 ->
  generic_eq (Regidx rs1z) zreg = true ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRRead = true ->
  exec (read_CSR csr) s = Some (readval, s) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec (csr_id_read_callback csr readval) s = Some (tt, s) ->
  exec (wX_bits (Regidx rd) readval) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr (Regidx rs1z) (Regidx rd) CSRRS) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hrs1 Hz Hpriv Hchk Hext Hread H344 H144 Hcb Hwx.
  unfold execute_CSRReg.
  replace (generic_eq (Regidx rs1z) zreg) with true by (symmetry; exact Hz).
  rewrite csr_access_type_CSRRS_true.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 rs1z s Hrs1)).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. cbn match.
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr else returnM (zeros' 64))
    with (read_CSR csr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hread).
  rewrite H344. rewrite H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM readval s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
    (_ : exec (Defs.bind0 (csr_id_read_callback csr readval) (wX_bits (Regidx rd) readval)) s
         = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _ Hcb). exact Hwx. }
  apply exec_returnM.
Qed.

(* ===== mstatus (0x300): machine CSR, accessible (vm), read = subrange of mstatus ===== *)
Definition csr_mstatus : mword 12 := Ox"300".
Definition mstatus_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mstatus s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_read_CSR_mstatus s :
  exec (read_CSR csr_mstatus) s = Some (mstatus_rdval s, s).
Proof.
  unfold read_CSR, csr_mstatus, mstatus_rdval.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300"))) with true
    by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_mstatus s :
  exec (check_CSR_result csr_mstatus Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result, csr_mstatus.
  assert (H : check_CSR (Ox"300") Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (check_CSR (Ox"300") Machine CSRRead) s = Some (true, s))).
  2:{ rewrite H. apply exec_returnm. }
  apply (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_csr_id_read_callback_mstatus s d :
  exec (csr_id_read_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mstatus_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mstatus (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv.
  apply (csrr_read_step csr_mstatus rs1z rd (mstatus_rdval s) s _ Hrs1 Hz Hpriv).
  - apply exec_check_CSR_result_mstatus.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mstatus.
  - rewrite (exec_wX_bits_gpr rd (mstatus_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* mstatus is untouched by the post-fetch sets, so its read value carries through. *)
Lemma mstatus_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  mstatus_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = mstatus_rdval s.
Proof.
  unfold mstatus_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section ForwardCsrrMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1z rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1z = 0.
  Hypothesis Hz : generic_eq (Regidx rs1z) zreg = true.
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), s0).

  Definition sAm0 : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcm0 : mstate := set_reg sAm0 nextPC (add_vec_int pc 4).
  Definition sXm0 : mstate :=
    set_reg s_pcm0 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s_pcm0)).
  Definition sTm0 : mstate := set_reg sXm0 PC (register_lookup nextPC sXm0.(sregs)).
  Definition sFm0 : mstate :=
    if b then set_reg sTm0 minstret (add_vec_int (register_lookup minstret sTm0.(sregs)) 1) else sTm0.

  Lemma forward_exec_csrr_mstatus_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFm0).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAm0.(sregs) = pc).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege sAm0.(sregs) = Machine).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA  : register_lookup hart_state sAm0.(sregs) = HART_ACTIVE tt).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAm0.(sregs))) ('b"1") = true).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAm0.(sregs))) ('b"1") = false).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp sAm0.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAm0 = Some (None, sAm0)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAm0 _ (exec_currentlyEnabled_S sAm0) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAm0 = Some (F_Base w, sAm0)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAm0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), sAm0))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege s_pcm0.(sregs) = Machine).
    { unfold s_pcm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS))) s_pcm0
              = Some (RETIRE_SUCCESS, sXm0)).
    { change (execute (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_mstatus (Regidx rs1z) (Regidx rd) CSRRS).
      unfold sXm0. exact (exec_execute_csrr_mstatus_gpr rs1z rd s_pcm0 Hrs1 Hz Hrd0 LprivC). }
    assert (Hha : exec (run_hart_active 0) sAm0
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXm0)).
    { exact (exec_hart_active_progress sAm0 sAm0 sXm0 sAm0 w
               (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXm0 w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXm0, s_pcm0, sAm0; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXm0, s_pcm0, sAm0; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrrMstatus.

Ltac reg_ne_m := solve [ vm_compute; reflexivity | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Ltac tmim0 := rewrite irrelevant_register_set; [ | reg_ne_m ].

Section CleanCsrrMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (mst0 : mword 64).
  Definition base_upd_m0 : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (mstatus_rdval (s_pcm0 s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcm0 : mstate :=
    if b then set_reg base_upd_m0 minstret (add_vec_int mst0 1) else base_upd_m0.

  Lemma sFm0_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFm0 s pc b rd = sFcm0.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXm0 s pc b rd).(sregs) = add_vec_int pc 4).
    { unfold sXm0; cbv zeta. unfold set_reg; cbn [sregs]. tmim0. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTm0 s pc b rd = base_upd_m0).
    { unfold sTm0. rewrite Enpc. unfold sXm0, s_pcm0, sAm0; cbv zeta.
      unfold base_upd_m0, s_pcm0, sAm0. reflexivity. }
    unfold sFm0, sFcm0. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_m0.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_m0, set_reg; cbn [sregs]. do 4 tmim0. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrrMstatus.

Section WpCsrrMstatus.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrr_mstatus_gpr (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HS Hpmaall Hpmpf Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : mstatus_rdval (s_pcm0 s pc b1) = subrange_vec_dec mstatus0 (Z.sub xlen 1) 0).
    { unfold s_pcm0, sAm0. rewrite mstatus_rdval_pcc. unfold mstatus_rdval. rewrite Lms. reflexivity. }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcm0 s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFm0_eq s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_mstatus_gpr s pc b1 w rs1z rd Hfetch_at Hsi_s Hrs1 Hz Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mstatus_rdval (s_pcm0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)) with "Hrdc") as "Hfile".
    unfold sFcm0, base_upd_m0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrMstatus.

(* ===== read_CSR reductions for the other readable CSRs (deterministic reads).
   Their check_CSR (accessibility) needs Ext_U (menvcfg/mcounteren), Ext_S (sie),
   or Ext_Zicntr+counter_enabled (time), so the full csrr WP for these is gated on
   those currentlyEnabled facts (left to the chain).  The READ itself is pinned. *)
(* Use `replace ... by (vm_compute; reflexivity)` (NOT `change`): `change g with
   true` records a regular cast that the kernel re-verifies with its slow default
   conversion at Qed (>3 min EACH for the read_CSR guard chains — the cause of the
   ~12min compile); `replace ... by (vm_compute; reflexivity)` emits a vm-cast the
   kernel checks with the bytecode machine (0.09s).  See iris-build-perf CASE 4. *)
(* Walk the [read_CSR] dispatch.  The common case is a non-matching guard, which
   we peel at the goal HEAD via [exec_if_false_g] (from WpEntry): no goal-wide
   [context] scan, no [cbn match] traversal of the huge term — see the README
   "Build-perf note".  The fallback branch is the original idiom, run only for the
   (few) [true] guards / any inner ifs, so behaviour is unchanged. *)
Ltac drive_csr :=
  unfold read_CSR;
  repeat first
    [ erewrite exec_if_false_g by (vm_compute; reflexivity)
    | match goal with
      | |- context[if ?g then _ else _] =>
          let v := eval vm_compute in g in
          lazymatch v with
          | true  => replace g with true by (vm_compute; reflexivity)
          | false => replace g with false by (vm_compute; reflexivity)
          end
      end; cbn match ].

Lemma exec_read_CSR_menvcfg s :
  exec (read_CSR (Ox"30A")) s
    = Some (subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_mcounteren s :
  exec (read_CSR (Ox"306")) s
    = Some (zero_extend' 64 (register_lookup mcounteren s.(sregs)), s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_sie s :
  exec (read_CSR (Ox"104")) s
    = Some (lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)), s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)). apply exec_returnM.
Qed.

Lemma exec_read_CSR_time s :
  exec (read_CSR (Ox"C01")) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mtime s)). apply exec_returnM. Qed.

(* ====================================================================== *)
(* Gated check_CSR_result engine for CSRRead (mirrors WpGprCsrw's csrw     *)
(* engine).  For CSRRead, check_CSR_priv/check_CSR_access are vm-true for   *)
(* our CSRs, stateen_allows = returnM true (default), so the only          *)
(* state-dependent gate is is_CSR_accessible = currentlyEnabled Ext_X.     *)
(* ====================================================================== *)
Lemma exec_check_CSR_read (csr : mword 12) s :
  exec (check_CSR_priv csr Machine) s = Some (true, s) ->
  check_CSR_access csr CSRRead = true ->
  exec (is_CSR_accessible csr Machine CSRRead) s = Some (true, s) ->
  exec (stateen_allows_CSR_access csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR csr Machine CSRRead) s = Some (true, s).
Proof.
  intros Hpriv Hca Hacc Hst. unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hpriv). cbn match.
  assert (HB : exec (returnM (check_CSR_access csr CSRRead) : M bool) s = Some (true, s))
    by (rewrite exec_returnm; rewrite Hca; reflexivity).
  rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hacc). cbn match.
  exact Hst.
Qed.

Lemma exec_check_CSR_result_read (csr : mword 12) s :
  exec (check_CSR csr Machine CSRRead) s = Some (true, s) ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro Hcc. unfold check_CSR_result.
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

(* currentlyEnabled Ext_U (mirrors WpGprMret / WpGprCsrw). *)
Lemma exec_hartSupports_U s : exec (hartSupports Ext_U) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_U s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_U) s = Some (true, s).
Proof.
  intro HU. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_U s)). cbn match.
  match goal with |- context[Defs.and_boolM ?l _] =>
    assert (Hu : exec l s = Some (true, s)) by
      (rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s));
       rewrite (exec_returnM _ s); rewrite HU; reflexivity);
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hu)
  end. cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicsr.
Qed.

(* ===== mcounteren (0x306): Ext_U-gated, read = zero_extend' 64 mcounteren ===== *)
Definition csr_mcounteren : mword 12 := Ox"306".
Definition mcounteren_rdval (s : mstate) : mword 64 :=
  zero_extend' 64 (register_lookup mcounteren s.(sregs)).

Lemma exec_check_CSR_result_mcounteren s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_mcounteren Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_mcounteren Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_mcounteren Machine CSRRead = currentlyEnabled Ext_U)
      by (vm_compute; reflexivity).
    rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
  - assert (H : stateen_allows_CSR_access csr_mcounteren Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_mcounteren s d :
  exec (csr_id_read_callback csr_mcounteren d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mcounteren d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mcounteren_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_mcounteren (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mcounteren_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv HU.
  apply (csrr_read_step csr_mcounteren rs1z rd (mcounteren_rdval s) s _ Hrs1 Hz Hpriv).
  - apply (exec_check_CSR_result_mcounteren s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mcounteren.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mcounteren.
  - rewrite (exec_wX_bits_gpr rd (mcounteren_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ====================================================================== *)
(* GENERIC forward + clean machinery for csrr (parametric over the CSR     *)
(* and its read-value function).  The execute step is supplied as a        *)
(* per-state hypothesis, so each CSR is a thin wrapper.                     *)
(* ====================================================================== *)
Section GenericForwardCsrr.
  Context (csr : mword 12) (rdval : mstate -> mword 64).
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1z rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr, Regidx rs1z, Regidx rd, CSRRS), s0).

  Definition sAg0 : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcg0 : mstate := set_reg sAg0 nextPC (add_vec_int pc 4).
  Definition sXg0 : mstate :=
    set_reg s_pcg0 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (rdval s_pcg0)).
  Definition sTg0 : mstate := set_reg sXg0 PC (register_lookup nextPC sXg0.(sregs)).
  Definition sFg0 : mstate :=
    if b then set_reg sTg0 minstret (add_vec_int (register_lookup minstret sTg0.(sregs)) 1) else sTg0.

  (* execute step at s_pcg0, supplied per-CSR *)
  Hypothesis Hexec_pcg0 :
    exec (execute_CSRReg csr (Regidx rs1z) (Regidx rd) CSRRS) s_pcg0 = Some (RETIRE_SUCCESS, sXg0).

  Lemma forward_exec_csrr_generic :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFg0).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAg0.(sregs) = pc).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege sAg0.(sregs) = Machine).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA  : register_lookup hart_state sAg0.(sregs) = HART_ACTIVE tt).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAg0.(sregs))) ('b"1") = true).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LS | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAg0.(sregs))) ('b"1") = false).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp sAg0.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAg0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAg0 = Some (None, sAg0)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAg0 _ (exec_currentlyEnabled_S sAg0) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAg0 = Some (F_Base w, sAg0)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAg0 = Some (CSRReg (csr, Regidx rs1z, Regidx rd, CSRRS), sAg0))
      by (apply Hdec; exact LprivA).
    assert (HexecC : exec (execute (CSRReg (csr, Regidx rs1z, Regidx rd, CSRRS))) s_pcg0
              = Some (RETIRE_SUCCESS, sXg0)).
    { change (execute (CSRReg (csr, Regidx rs1z, Regidx rd, CSRRS)))
        with (execute_CSRReg csr (Regidx rs1z) (Regidx rd) CSRRS).
      exact Hexec_pcg0. }
    assert (Hha : exec (run_hart_active 0) sAg0
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXg0)).
    { exact (exec_hart_active_progress sAg0 sAg0 sXg0 sAg0 w
               (CSRReg (csr, Regidx rs1z, Regidx rd, CSRRS)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXg0 w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXg0, s_pcg0, sAg0; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXg0, s_pcg0, sAg0; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End GenericForwardCsrr.

Section GenericCleanCsrr.
  Context (rdval : mstate -> mword 64).
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (mst0 : mword 64).
  Definition base_upd_g0 : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (rdval (s_pcg0 s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcg0 : mstate :=
    if b then set_reg base_upd_g0 minstret (add_vec_int mst0 1) else base_upd_g0.

  Lemma sFg0_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFg0 rdval s pc b rd = sFcg0.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXg0 rdval s pc b rd).(sregs) = add_vec_int pc 4).
    { unfold sXg0; cbv zeta. unfold set_reg; cbn [sregs]. tmim0. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTg0 rdval s pc b rd = base_upd_g0).
    { unfold sTg0. rewrite Enpc. unfold sXg0, s_pcg0, sAg0; cbv zeta.
      unfold base_upd_g0, s_pcg0, sAg0. reflexivity. }
    unfold sFg0, sFcg0. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_g0.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_g0, set_reg; cbn [sregs]. do 4 tmim0. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End GenericCleanCsrr.

(* ===== mcounteren: read value survives the post-fetch sets ===== *)
Lemma mcounteren_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  mcounteren_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = mcounteren_rdval s.
Proof.
  unfold mcounteren_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Lemma misa_U_pcg0 (s : mstate) (pc : mword 64) (b : bool) :
  eq_vec (_get_Misa_U (register_lookup misa (s_pcg0 s pc b).(sregs))) ('b"1")
    = eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1").
Proof.
  unfold s_pcg0, sAg0, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section WpCsrrMcounteren.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrr_mcounteren_gpr (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 mdv0 : mword 64) (mcen0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mcounteren, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ mcounteren ↦ᵣ mcen0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (zero_extend' 64 mcen0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ mcounteren ↦ᵣ mcen0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HU HS Hpmaall Hpmpf Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmcen")  as %Lmcen.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : mcounteren_rdval (s_pcg0 s pc b1) = zero_extend' 64 mcen0).
    { rewrite mcounteren_rdval_pcc. unfold mcounteren_rdval. rewrite Lmcen. reflexivity. }
    assert (HUc : eq_vec (_get_Misa_U (register_lookup misa (s_pcg0 s pc b1).(sregs))) ('b"1") = true).
    { rewrite misa_U_pcg0. rewrite Lmisa. exact HU. }
    assert (Hprivc : register_lookup cur_privilege (s_pcg0 s pc b1).(sregs) = Machine).
    { unfold s_pcg0, sAg0, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lpriv. }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg0 mcounteren_rdval s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg0_eq mcounteren_rdval s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_generic csr_mcounteren mcounteren_rdval s pc b1 w rs1z rd
               Hfetch_at Hsi_s Hdec
               (exec_execute_csrr_mcounteren_gpr rs1z rd (s_pcg0 s pc b1) Hrs1 Hz Hrd Hprivc HUc)
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mcounteren_rdval (s_pcg0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (zero_extend' 64 mcen0)) with "Hrdc") as "Hfile".
    unfold sFcg0, base_upd_g0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
  Lemma wp_csrr_mcounteren_gpr_2 (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 mdv0 : mword 64) (mcen0 : mword 32)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mcounteren, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ mcounteren ↦ᵣ mcen0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (zero_extend' 64 mcen0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ mcounteren ↦ᵣ mcen0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HU HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmcen")  as %Lmcen.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : mcounteren_rdval (s_pcg0 s pc b1) = zero_extend' 64 mcen0).
    { rewrite mcounteren_rdval_pcc. unfold mcounteren_rdval. rewrite Lmcen. reflexivity. }
    assert (HUc : eq_vec (_get_Misa_U (register_lookup misa (s_pcg0 s pc b1).(sregs))) ('b"1") = true).
    { rewrite misa_U_pcg0. rewrite Lmisa. exact HU. }
    assert (Hprivc : register_lookup cur_privilege (s_pcg0 s pc b1).(sregs) = Machine).
    { unfold s_pcg0, sAg0, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lpriv. }
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg0 mcounteren_rdval s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg0_eq mcounteren_rdval s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_generic csr_mcounteren mcounteren_rdval s pc b1 w rs1z rd
               Hfetch_at Hsi_s Hdec
               (exec_execute_csrr_mcounteren_gpr rs1z rd (s_pcg0 s pc b1) Hrs1 Hz Hrd Hprivc HUc)
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mcounteren_rdval (s_pcg0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (zero_extend' 64 mcen0)) with "Hrdc") as "Hfile".
    unfold sFcg0, base_upd_g0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmcen Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrMcounteren.

(* ===== menvcfg (0x30A): Ext_U-gated, read = subrange of menvcfg ===== *)
Definition csr_menvcfg : mword 12 := Ox"30A".
Definition menvcfg_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_check_CSR_result_menvcfg s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_menvcfg Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HU. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_menvcfg Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_menvcfg Machine CSRRead = currentlyEnabled Ext_U)
      by (vm_compute; reflexivity).
    rewrite Hacceq. apply (exec_currentlyEnabled_U s HU).
  - assert (H : stateen_allows_CSR_access csr_menvcfg Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_menvcfg s d :
  exec (csr_id_read_callback csr_menvcfg d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_menvcfg d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_menvcfg_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_menvcfg (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (menvcfg_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv HU.
  apply (csrr_read_step csr_menvcfg rs1z rd (menvcfg_rdval s) s _ Hrs1 Hz Hpriv).
  - apply (exec_check_CSR_result_menvcfg s HU).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_menvcfg.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_menvcfg.
  - rewrite (exec_wX_bits_gpr rd (menvcfg_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma menvcfg_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  menvcfg_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = menvcfg_rdval s.
Proof.
  unfold menvcfg_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section WpCsrrMenvcfg.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrr_menvcfg_gpr (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 menvcfg0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_U misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_menvcfg, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ menvcfg ↦ᵣ menvcfg0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HU HS Hpmaall Hpmpf Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hmenv Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmenv")  as %Lmenv.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : menvcfg_rdval (s_pcg0 s pc b1) = subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0).
    { rewrite menvcfg_rdval_pcc. unfold menvcfg_rdval. rewrite Lmenv. reflexivity. }
    assert (HUc : eq_vec (_get_Misa_U (register_lookup misa (s_pcg0 s pc b1).(sregs))) ('b"1") = true).
    { rewrite misa_U_pcg0. rewrite Lmisa. exact HU. }
    assert (Hprivc : register_lookup cur_privilege (s_pcg0 s pc b1).(sregs) = Machine).
    { unfold s_pcg0, sAg0, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lpriv. }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg0 menvcfg_rdval s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg0_eq menvcfg_rdval s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_generic csr_menvcfg menvcfg_rdval s pc b1 w rs1z rd
               Hfetch_at Hsi_s Hdec
               (exec_execute_csrr_menvcfg_gpr rs1z rd (s_pcg0 s pc b1) Hrs1 Hz Hrd Hprivc HUc)
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (menvcfg_rdval (s_pcg0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (subrange_vec_dec menvcfg0 (Z.sub xlen 1) 0)) with "Hrdc") as "Hfile".
    unfold sFcg0, base_upd_g0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmenv Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmenv Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrMenvcfg.

(* ===== sie (0x104): Ext_S-gated, read = lower_mie mie mideleg (TWO regs) ===== *)
Definition csr_sie : mword 12 := Ox"104".
Definition sie_rdval (s : mstate) : mword 64 :=
  lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)).

Lemma exec_check_CSR_result_sie s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_sie Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS. apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_sie Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hacceq : is_CSR_accessible csr_sie Machine CSRRead = currentlyEnabled Ext_S)
      by (vm_compute; reflexivity).
    rewrite Hacceq. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_sie Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_sie s d :
  exec (csr_id_read_callback csr_sie d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sie d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_sie_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_sie (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sie_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv HS.
  apply (csrr_read_step csr_sie rs1z rd (sie_rdval s) s _ Hrs1 Hz Hpriv).
  - apply (exec_check_CSR_result_sie s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_sie.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_sie.
  - rewrite (exec_wX_bits_gpr rd (sie_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma sie_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  sie_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = sie_rdval s.
Proof.
  unfold sie_rdval, set_reg; cbn [sregs].
  do 4 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Lemma misa_S_pcg0 (s : mstate) (pc : mword 64) (b : bool) :
  eq_vec (_get_Misa_S (register_lookup misa (s_pcg0 s pc b).(sregs))) ('b"1")
    = eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1").
Proof.
  unfold s_pcg0, sAg0, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section WpCsrrSie.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrr_sie_gpr_2 (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 mie0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_sie, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ mie ↦ᵣ mie0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (lower_mie mie0 mdv0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ mie ↦ᵣ mie0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hmie Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmie")   as %Lmie.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : sie_rdval (s_pcg0 s pc b1) = lower_mie mie0 mdv0).
    { rewrite sie_rdval_pcc. unfold sie_rdval. rewrite Lmie Lmdl. reflexivity. }
    assert (HSc : eq_vec (_get_Misa_S (register_lookup misa (s_pcg0 s pc b1).(sregs))) ('b"1") = true).
    { rewrite misa_S_pcg0. rewrite Lmisa. exact HS. }
    assert (Hprivc : register_lookup cur_privilege (s_pcg0 s pc b1).(sregs) = Machine).
    { unfold s_pcg0, sAg0, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lpriv. }
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg0 sie_rdval s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg0_eq sie_rdval s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_generic csr_sie sie_rdval s pc b1 w rs1z rd
               Hfetch_at Hsi_s Hdec
               (exec_execute_csrr_sie_gpr rs1z rd (s_pcg0 s pc b1) Hrs1 Hz Hrd Hprivc HSc)
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sie_rdval (s_pcg0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (lower_mie mie0 mdv0)) with "Hrdc") as "Hfile".
    unfold sFcg0, base_upd_g0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmie Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmie Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrSie.

(* ===== time (0xC01): Ext_Zicntr-gated + counter_enabled 1 priv.           *)
(* At Machine privilege feature_enabled_for_priv = FEATURE_ENABLED          *)
(* unconditionally, so counter_enabled 1 Machine = returnM true (after      *)
(* reading mcounteren/scounteren, values ignored).  Thus the gate is just   *)
(* currentlyEnabled Ext_Zicntr, which holds for ANY state (hartSupports     *)
(* Zicntr = true). Read = subrange of mtime. ===== *)
Definition csr_time : mword 12 := Ox"C01".
Definition time_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_hartSupports_Zicntr s : exec (hartSupports Ext_Zicntr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zicntr s :
  exec (currentlyEnabled Ext_Zicntr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicntr s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicntr.
Qed.

(* counter_enabled index Machine = returnM true (reads mcounteren/scounteren, ignores). *)
Lemma exec_counter_enabled_machine (index : Z) s :
  exec (counter_enabled index Machine) s = Some (true, s).
Proof.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)).
  unfold feature_enabled_for_priv_bool.
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (feature_enabled_for_priv Machine _ _ _) s = Some (FEATURE_ENABLED, s))).
  2:{ unfold feature_enabled_for_priv. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_time s :
  exec (is_CSR_accessible csr_time Machine CSRRead) s = Some (true, s).
Proof.
  assert (Hred : is_CSR_accessible csr_time Machine CSRRead
                 = Defs.and_boolM (currentlyEnabled Ext_Zicntr) (counter_enabled 1 Machine))
    by (vm_compute; reflexivity).
  rewrite Hred.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr s)). cbn match.
  apply exec_counter_enabled_machine.
Qed.

Lemma exec_check_CSR_result_time s :
  exec (check_CSR_result csr_time Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  apply exec_check_CSR_result_read. apply exec_check_CSR_read.
  - assert (H : check_CSR_priv csr_time Machine = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_time.
  - assert (H : stateen_allows_CSR_access csr_time Machine CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_csr_id_read_callback_time s d :
  exec (csr_id_read_callback csr_time d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_time d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_time_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_time (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (time_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv.
  apply (csrr_read_step csr_time rs1z rd (time_rdval s) s _ Hrs1 Hz Hpriv).
  - apply (exec_check_CSR_result_time s).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_time.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_time.
  - rewrite (exec_wX_bits_gpr rd (time_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

Lemma time_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  time_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = time_rdval s.
Proof.
  unfold time_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section WpCsrrTime.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_csrr_time_gpr_2 (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mstatus0 misa0 mtime0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j) ->
    (forall j : nat, (N.of_nat j < 2)%N ->
       nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j)) ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_time, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ mtime ↦ᵣ mtime0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)]> m) -∗
        reg_pointsto misa dqc misa0 -∗ mtime ↦ᵣ mtime0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrs1 Hz Hrd Hmd HS Hpmaall Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
             Hconcat Haddr Hlo Hhi HmisaC Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hmtime Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 2) as (regl & Hml & Hxl & _ & _).
    destruct (Hpmaall (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh & Hxh & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmtime") as %Lmtime.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : time_rdval (s_pcg0 s pc b1) = subrange_vec_dec mtime0 (Z.sub xlen 1) 0).
    { rewrite time_rdval_pcc. unfold time_rdval. rewrite Lmtime. reflexivity. }
    assert (Hprivc : register_lookup cur_privilege (s_pcg0 s pc b1).(sregs) = Machine).
    { unfold s_pcg0, sAg0, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Lpriv. }
    iEval (rewrite <- Lmisa) in "Hmisa".
    iDestruct (fetch_from_pts_minstret_2 pc w regl regh pmpcfg0 pmar0 b1 s
                 Hml Hmh Hxl Hxh Hpmpf Hal2l Hal2h Hbit0f Hbit1f Hvalignf HnotRVCf
                 Hconcat Haddr Hlo Hhi ltac:(rewrite Lmisa; exact HmisaC)
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcg0 time_rdval s pc b1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFg0_eq time_rdval s pc b1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_csrr_generic csr_time time_rdval s pc b1 w rs1z rd
               Hfetch_at Hsi_s Hdec
               (exec_execute_csrr_time_gpr rs1z rd (s_pcg0 s pc b1) Hrs1 Hz Hrd Hprivc)
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iEval (rewrite Lmisa) in "Hmisa".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (time_rdval (s_pcg0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (subrange_vec_dec mtime0 (Z.sub xlen 1) 0)) with "Hrdc") as "Hfile".
    unfold sFcg0, base_upd_g0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmtime Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hmtime Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrTime.

(* ===== Demonstration: ONE wp_csrr_mstatus_gpr at two different destinations. ===== *)
Section WpCsrrMstatusDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition wp_csrr_mstatus_x15 (pc : mword 64) (w : mword 32) := wp_csrr_mstatus_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 0) (mword_of_int 15).
  Definition wp_csrr_mstatus_x5  (pc : mword 64) (w : mword 32) := wp_csrr_mstatus_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 0) (mword_of_int 5).
End WpCsrrMstatusDemo.
